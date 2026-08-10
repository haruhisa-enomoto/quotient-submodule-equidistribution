#!/usr/bin/env python3
"""Fail fast when the public release boundary or theorem map drifts."""

from __future__ import annotations

from html.parser import HTMLParser
import json
from pathlib import Path
import re
import sys
import tomllib
from urllib.parse import urlsplit

ROOT = Path(__file__).resolve().parents[1]
EXPECTED_MATHLIB = "28313485bc624fcd16dcb162dd2e2c3c813aa8fe"
EXPECTED_GRAPHS = {
    "main-theorem.html",
    "first-last-four.html",
    "nakayama.html",
    "radical-square-zero.html",
    "representation-directed.html",
    "generator-minimal.html",
}


def fail(message: str) -> None:
    raise SystemExit(f"release check failed: {message}")


def lean_without_comments_and_strings(text: str) -> str:
    """Erase nested Lean comments and strings, preserving line breaks."""
    out: list[str] = []
    i = 0
    depth = 0
    in_string = False
    escaped = False
    while i < len(text):
        pair = text[i : i + 2]
        char = text[i]
        if depth:
            if pair == "/-":
                depth += 1
                out.extend("  ")
                i += 2
            elif pair == "-/":
                depth -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if char == "\n" else " ")
                i += 1
            continue
        if in_string:
            out.append("\n" if char == "\n" else " ")
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            i += 1
            continue
        if pair == "/-":
            depth = 1
            out.extend("  ")
            i += 2
        elif pair == "--":
            end = text.find("\n", i)
            if end == -1:
                out.extend(" " * (len(text) - i))
                break
            out.extend(" " * (end - i))
            i = end
        elif char == '"':
            in_string = True
            out.append(" ")
            i += 1
        else:
            out.append(char)
            i += 1
    if depth or in_string:
        fail("unterminated comment or string in Lean source")
    return "".join(out)


def production_lean_files() -> list[Path]:
    files = sorted((ROOT / "QuotientSubmoduleEquidistribution").rglob("*.lean"))
    files.extend(path for path in (ROOT / "QuotientSubmoduleEquidistribution.lean", ROOT / "MainResults.lean", ROOT / "Audit.lean") if path.exists())
    return files


def check_production_sources() -> None:
    files = production_lean_files()
    if not files:
        fail("no production Lean sources found")
    forbidden = re.compile(r"\b(?:sorry|admit|axiom)\b")
    tauceti_import = re.compile(r"(?m)^\s*import\s+TauCeti(?:\.|\s|$)")
    for path in files:
        text = path.read_text(encoding="utf-8")
        code = lean_without_comments_and_strings(text)
        match = forbidden.search(code)
        if match:
            fail(f"forbidden production token {match.group(0)!r} in {path.relative_to(ROOT)}")
        if tauceti_import.search(code):
            fail(f"TauCeti import in {path.relative_to(ROOT)}")


def check_dependencies() -> None:
    with (ROOT / "lakefile.toml").open("rb") as handle:
        lake = tomllib.load(handle)
    requirements = lake.get("require", [])
    if len(requirements) != 1 or requirements[0].get("name") != "mathlib":
        fail("the production Lake project must directly require exactly Mathlib")
    if requirements[0].get("rev") != EXPECTED_MATHLIB:
        fail("unexpected Mathlib revision in lakefile.toml")
    manifest = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8"))
    direct = [package for package in manifest["packages"] if not package.get("inherited", False)]
    if [(package["name"], package["rev"]) for package in direct] != [("mathlib", EXPECTED_MATHLIB)]:
        fail("lake-manifest.json has an unexpected direct package")


def yaml_targets() -> list[tuple[str, Path, Path | None]]:
    text = (ROOT / "formalization.yaml").read_text(encoding="utf-8")
    if not text.startswith('version: "v0.3"'):
        fail("formalization.yaml is not v0.3")
    try:
        main_section = text.split("  main_results:\n", 1)[1].split("\nreview:\n", 1)[0]
    except IndexError:
        fail("formalization.yaml has no parseable main_results section")
    targets: list[tuple[str, Path, Path | None]] = []
    for block in re.split(r"(?m)(?=^    - name:)", main_section):
        if not block.lstrip().startswith("- name:"):
            continue
        declaration = re.search(r'^\s+declaration: "([^"]+)"$', block, re.MULTILINE)
        file_name = re.search(r'^\s+file: "([^"]+)"$', block, re.MULTILINE)
        sorry_count = re.search(r'^\s+sorry_count: 0$', block, re.MULTILINE)
        axioms = re.search(r'^\s+axioms: \[[^\]]+\]$', block, re.MULTILINE)
        comparator = re.search(r'^\s+comparator_config: "([^"]+)"$', block, re.MULTILINE)
        if not all((declaration, file_name, sorry_count, axioms)):
            fail("malformed main-result block in formalization.yaml")
        config_path = ROOT / comparator.group(1) if comparator else None
        targets.append((declaration.group(1), ROOT / file_name.group(1), config_path))
    if len(targets) != 6:
        fail(f"expected 6 advertised targets, found {len(targets)}")
    return targets


def check_targets() -> None:
    main_results = (ROOT / "MainResults.lean").read_text(encoding="utf-8")
    audit = (ROOT / "Audit.lean").read_text(encoding="utf-8")
    for declaration, source, config_path in yaml_targets():
        if not source.is_file():
            fail(f"missing target source {source.relative_to(ROOT)}")
        final_name = declaration.rsplit(".", 1)[-1]
        source_code = lean_without_comments_and_strings(source.read_text(encoding="utf-8"))
        if not re.search(rf"\b(?:theorem|def|inductive)\s+{re.escape(final_name)}\b", source_code):
            fail(f"declaration {declaration} is not found in its advertised source")
        if declaration not in main_results:
            fail(f"{declaration} is missing from MainResults.lean")
        if f"#print axioms {declaration}" not in audit:
            fail(f"{declaration} is missing from Audit.lean")
        if config_path is None:
            challenge_name = "MainTheorem.lean" if ".MainTheoremEndpoint." in declaration else "FirstLastFour.lean"
            challenge = ROOT / "verification" / "ComparatorChallenges" / challenge_name
            challenge_code = lean_without_comments_and_strings(challenge.read_text(encoding="utf-8")) if challenge.is_file() else ""
            if not re.search(rf"\btheorem\s+{re.escape(final_name)}\b", challenge_code):
                fail(f"missing independent target statement for {declaration}")
            continue
        if not config_path.is_file():
            fail(f"missing Comparator config {config_path.relative_to(ROOT)}")
        config = json.loads(config_path.read_text(encoding="utf-8"))
        if declaration not in config.get("theorem_names", []):
            fail(f"{declaration} is missing from {config_path.relative_to(ROOT)}")
        challenge = ROOT / "verification" / Path(*config["challenge_module"].split(".")).with_suffix(".lean")
        if not challenge.is_file():
            fail(f"missing challenge module {challenge.relative_to(ROOT)}")
        solution_import = f'import {config["solution_module"]}'
        if solution_import in challenge.read_text(encoding="utf-8"):
            fail(f"challenge imports its solution: {challenge.relative_to(ROOT)}")


class LinkCollector(HTMLParser):
    def __init__(self) -> None:
        super().__init__()
        self.links: list[str] = []

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        for key, value in attrs:
            if value and ((tag == "a" and key == "href") or (tag in {"link", "script", "img"} and key in {"href", "src"})):
                self.links.append(value)


def check_site() -> None:
    site = ROOT / "website"
    graph_dir = site / "import-graphs"
    missing_graphs = sorted(EXPECTED_GRAPHS - {path.name for path in graph_dir.glob("*.html")})
    if missing_graphs:
        fail(f"missing generated import graphs: {', '.join(missing_graphs)}")
    for page in sorted(site.glob("*.html")):
        text = page.read_text(encoding="utf-8")
        parser = LinkCollector()
        parser.feed(text)
        for link in parser.links:
            parsed = urlsplit(link)
            if parsed.scheme or link.startswith("//") or not parsed.path:
                continue
            if parsed.path.startswith("api/"):
                continue
            target = (page.parent / parsed.path).resolve()
            try:
                target.relative_to(site.resolve())
            except ValueError:
                fail(f"site link escapes website/: {page.name} -> {link}")
            if not target.exists():
                fail(f"broken site link: {page.name} -> {link}")
        without_display = re.sub(r"\$\$.*?\$\$", "", text, flags=re.DOTALL)
        if text.count("$$") % 2 or len(re.findall(r"(?<!\\)\$", without_display)) % 2:
            fail(f"unbalanced MathJax delimiters in {page.name}")


def check_release_files() -> None:
    for name in ("README.md", "LICENSE", "NOTICE", "PROVENANCE.md", "TRUST.md", "formalization.yaml"):
        if not (ROOT / name).is_file():
            fail(f"missing {name}")


def main() -> None:
    check_release_files()
    check_dependencies()
    check_production_sources()
    check_targets()
    check_site()
    print(f"release check passed: {len(production_lean_files())} production Lean files, 6 advertised targets")


if __name__ == "__main__":
    main()
