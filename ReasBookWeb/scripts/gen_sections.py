#!/usr/bin/env python3
"""Generate ReasBookSite/Sections.lean from the current ReasBook module tree."""

from __future__ import annotations

import argparse
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable

SITE_BASE = "https://optsuite.github.io/ReasBook/"
DOCS_BASE = f"{SITE_BASE}docs/"
GITHUB_SOURCE_BASE = "https://github.com/optsuite/ReasBook/blob/main/ReasBook/"

BOOK_TITLES = {
    "ConvexAnalysis_Rockafellar_1970": "Convex Analysis (Rockafellar, 1970)",
    "IntegerProgramming_Conforti_2014": "Integer Programming (Conforti et al., 2014)",
    "Analysis2_Tao_2022": "Analysis II (Tao, 2022)",
    "IntroductiontoRealAnalysisVolumeI_JiriLebl_2025": "Introduction to Real Analysis, Volume I (Jiri Lebl, 2025)",
}

PAPER_TITLES = {
    "SmoothMinimization_Nesterov_2004": "Smooth Minimization (Nesterov, 2004)",
    "OnSomeLocalRings_Maassaran_2025": "On Some Local Rings (Maassaran, 2025)",
}

TBD_BOOKS = {"IntegerProgramming_Conforti_2014"}

SKIP_STEMS = {"utils", "tactics", "scratch", "internal", "helper", "helpers"}

CHAPTER_RE = re.compile(r"^(?:chapter_|chap)(\d+)$", re.IGNORECASE)
SECTION_RE = re.compile(r"^section_?(\d+)$", re.IGNORECASE)
PART_RE = re.compile(r"^part_?(\d+)$", re.IGNORECASE)


@dataclass(frozen=True)
class Entry:
    category: str
    module: str
    title: str
    route: str
    book_or_paper: str
    chapter_num: int
    section_num: int
    part_num: int
    stem: str
    is_home: bool


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "repo_root",
        nargs="?",
        default=None,
        help="Path to the ReasBook repo root (the directory containing ReasBookWeb/ and ReasBook/).",
    )
    return parser.parse_args()


def humanize_identifier(s: str) -> str:
    s = s.replace("_", " ")
    s = re.sub(r"\s+", " ", s).strip()
    return s.title() if s else s


def module_doc_title(path: Path) -> str | None:
    text = path.read_text(encoding="utf-8", errors="ignore")
    m = re.search(r"/(?:-!|--)\s*(.*?)\s*-/", text, re.DOTALL)
    if not m:
        return None
    body = m.group(1)
    lines = []
    for raw in body.splitlines():
        line = raw.strip().lstrip("#").strip()
        if not line:
            continue
        if line.startswith("import "):
            continue
        lines.append(line)
    if not lines:
        return None
    first = lines[0]
    if len(first) > 60:
        return None
    if "`" in first or ":" in first or "." in first:
        return None
    if len(first.split()) > 8:
        return None
    if not re.match(r"^(Section|Chapter|Appendix)\\b", first, re.IGNORECASE):
        return None
    return first


def chapter_number(parts: Iterable[str]) -> int:
    for p in parts:
        m = CHAPTER_RE.match(p)
        if m:
            return int(m.group(1))
    return 0


def chapter_title(parts: Iterable[str]) -> str | None:
    for p in parts:
        m = CHAPTER_RE.match(p)
        if m:
            return f"Chapter {int(m.group(1)):02d}"
    return None


def parse_section_part(stem: str) -> tuple[int, int]:
    section_num = 0
    part_num = 0
    lower = stem.lower()
    for token in lower.split("_"):
        ms = SECTION_RE.match(token)
        if ms:
            section_num = int(ms.group(1))
            continue
        mp = PART_RE.match(token)
        if mp:
            part_num = int(mp.group(1))
    m2 = re.match(r"section(\d+)", lower)
    if m2:
        section_num = int(m2.group(1))
    m3 = re.search(r"part(\d+)", lower)
    if m3:
        part_num = int(m3.group(1))
    return section_num, part_num


def section_title_from_stem(stem: str) -> str:
    lower = stem.lower()
    if lower in {"paper", "main"}:
        return "Overview"

    sec, part = parse_section_part(stem)
    if sec > 0:
        base = f"Section {sec:02d}"
        if part > 0:
            return f"{base} -- Part {part}"
        return base

    return humanize_identifier(stem)


def book_title(book: str) -> str:
    if book in BOOK_TITLES:
        return BOOK_TITLES[book]
    return humanize_identifier(book)


def paper_title(paper: str) -> str:
    if paper in PAPER_TITLES:
        return PAPER_TITLES[paper]
    return humanize_identifier(paper)


def to_module(source_root: Path, path: Path) -> str:
    rel = path.relative_to(source_root)
    return ".".join(rel.with_suffix("").parts)


def normalize_path(path: str) -> str:
    path = path.strip()
    if not path:
        return ""
    has_trailing_slash = path.endswith("/")
    pieces = [piece for piece in path.split("/") if piece]
    if not pieces:
        return ""
    out = "/".join(pieces)
    if has_trailing_slash:
        out += "/"
    return out


def route_from_module(module: str) -> str:
    return normalize_path("/".join(part.lower() for part in module.split(".")) + "/")


def should_include_book(path: Path) -> bool:
    stem = path.stem.lower()
    if stem in SKIP_STEMS:
        return False

    parts_lower = [p.lower() for p in path.parts]
    in_chapter_tree = any(CHAPTER_RE.match(p) for p in parts_lower)
    if not in_chapter_tree:
        return False

    if stem.startswith("section"):
        return True

    return module_doc_title(path) is not None


def should_include_paper(path: Path) -> bool:
    stem = path.stem.lower()
    if stem in SKIP_STEMS:
        return False
    if stem in {"paper", "main"}:
        return True
    return stem.startswith("section")


def collect_entries(source_root: Path) -> list[Entry]:
    entries: list[Entry] = []

    books_root = source_root / "Books"
    papers_root = source_root / "Papers"

    for book_dir in sorted([p for p in books_root.iterdir() if p.is_dir()]):
        book = book_dir.name
        if book in TBD_BOOKS:
            continue
        module = f"Books.{book}.VersoHome"
        entries.append(
            Entry(
                category="books",
                module=module,
                title=f"{book_title(book)} -- Home",
                route=normalize_path(f"books/{book.lower()}/home/"),
                book_or_paper=book,
                chapter_num=0,
                section_num=0,
                part_num=0,
                stem="versohome",
                is_home=True,
            )
        )

    for path in sorted(books_root.rglob("*.lean")):
        if not should_include_book(path):
            continue
        rel = path.relative_to(books_root)
        book = rel.parts[0]
        if book in TBD_BOOKS:
            continue
        ch_title = chapter_title(rel.parts)
        sec_title = module_doc_title(path) or section_title_from_stem(path.stem)
        title_parts = [book_title(book)]
        if ch_title:
            title_parts.append(ch_title)
        title_parts.append(sec_title)
        sec_num, part_num = parse_section_part(path.stem)
        entries.append(
            Entry(
                category="books",
                module=to_module(source_root, path),
                title=" -- ".join(title_parts),
                route=route_from_module(to_module(source_root, path)),
                book_or_paper=book,
                chapter_num=chapter_number(rel.parts),
                section_num=sec_num,
                part_num=part_num,
                stem=path.stem.lower(),
                is_home=False,
            )
        )

    for paper_dir in sorted([p for p in papers_root.iterdir() if p.is_dir()]):
        paper = paper_dir.name
        module = f"Papers.{paper}.VersoHome"
        entries.append(
            Entry(
                category="papers",
                module=module,
                title=f"{paper_title(paper)} -- Home",
                route=normalize_path(f"papers/{paper.lower()}/home/"),
                book_or_paper=paper,
                chapter_num=0,
                section_num=0,
                part_num=0,
                stem="versohome",
                is_home=True,
            )
        )

    for path in sorted(papers_root.rglob("*.lean")):
        if not should_include_paper(path):
            continue
        rel = path.relative_to(papers_root)
        paper = rel.parts[0]
        sec_title = module_doc_title(path) or section_title_from_stem(path.stem)
        sec_num, part_num = parse_section_part(path.stem)
        entries.append(
            Entry(
                category="papers",
                module=to_module(source_root, path),
                title=f"{paper_title(paper)} -- {sec_title}",
                route=route_from_module(to_module(source_root, path)),
                book_or_paper=paper,
                chapter_num=0,
                section_num=sec_num,
                part_num=part_num,
                stem=path.stem.lower(),
                is_home=False,
            )
        )

    entries.sort(
        key=lambda e: (
            0 if e.category == "books" else 1,
            e.book_or_paper.lower(),
            0 if e.is_home else 1,
            e.chapter_num,
            e.section_num,
            e.part_num,
            e.stem,
        )
    )
    return entries


def lean_string(s: str) -> str:
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'


def emit_sections(entries: list[Entry]) -> str:
    lines: list[str] = []
    lines.append("-- This file is generated by scripts/gen_sections.py")
    lines.append("-- Do not edit manually.")
    lines.append("")
    lines.append("namespace ReasBookSite.Sections")
    lines.append("")
    lines.append("def sections : Array (Lean.Name × String) := #[")
    for e in entries:
        lines.append(f"  (`{e.module}, {lean_string(e.title)}),")
    lines.append("]")
    lines.append("")
    lines.append("def routes : Array (String × Lean.Name) := #[")
    for e in entries:
        lines.append(f"  ({lean_string(e.route)}, `{e.module}),")
    lines.append("]")
    lines.append("")
    lines.append("end ReasBookSite.Sections")
    lines.append("")
    return "\n".join(lines)


def emit_route_table(entries: list[Entry]) -> str:
    lines: list[str] = []
    lines.append("-- This file is generated by scripts/gen_sections.py")
    lines.append("-- Do not edit manually.")
    lines.append("")
    lines.append("import VersoBlog")
    lines.append("import ReasBookSite.Home")
    lines.append("import Book")
    lines.append("")
    lines.append("open Verso Genre Blog Site Syntax")
    lines.append("")
    lines.append("namespace ReasBookSite.RouteTable")
    lines.append("")
    lines.append("scoped syntax \"reasbook_site_dir\" : dir_spec")
    lines.append("")
    lines.append("macro_rules")
    lines.append("  | `(dir_spec| reasbook_site_dir) =>")
    lines.append("    `(dir_spec| /")
    lines.append('      static "static" ← "./static_files"')
    for e in entries:
        lines.append(f"      {lean_string(e.route)} Book.{e.module}")
    lines.append("    )")
    lines.append("")
    lines.append("def reasbook_site : Site := site ReasBookSite.Home /")
    lines.append('  static "static" ← "./static_files"')
    for e in entries:
        lines.append(f"  {lean_string(e.route)} Book.{e.module}")
    lines.append("")
    lines.append("end ReasBookSite.RouteTable")
    lines.append("")
    return "\n".join(lines)


def doc_link(module: str) -> str:
    return f"{DOCS_BASE}{module.replace('.', '/')}.html"


def source_link(module: str) -> str:
    return f"{GITHUB_SOURCE_BASE}{module.replace('.', '/')}.lean"


def verso_link(route: str) -> str:
    return f"{SITE_BASE}{route}"


def chapter_label(chapter_num: int) -> str:
    return f"Chapter {chapter_num:02d} (TODO: replace with chapter title)"


def write_verso_home_modules(source_root: Path, entries: list[Entry]) -> None:
    books_root = source_root / "Books"
    papers_root = source_root / "Papers"
    by_book: dict[str, list[Entry]] = {}
    by_paper: dict[str, list[Entry]] = {}
    for e in entries:
        if e.is_home:
            continue
        if e.category == "books":
            by_book.setdefault(e.book_or_paper, []).append(e)
        elif e.category == "papers":
            by_paper.setdefault(e.book_or_paper, []).append(e)

    for book in sorted([p.name for p in books_root.iterdir() if p.is_dir()]):
        if book in TBD_BOOKS:
            continue
        item_entries = by_book.get(book, [])
        item_entries = sorted(item_entries, key=lambda e: (e.chapter_num, e.section_num, e.part_num, e.stem))
        lines: list[str] = []
        lines.append("/-!")
        lines.append(f"# {book_title(book)}")
        lines.append("")
        lines.append("This page provides an overview and navigation links for this book.")
        lines.append("")
        if not item_entries:
            lines.append("No chapter or section pages have been generated yet.")
            lines.append("")
        else:
            current_chapter = None
            for e in item_entries:
                if current_chapter != e.chapter_num:
                    current_chapter = e.chapter_num
                    lines.append(f"## {chapter_label(current_chapter)}")
                    lines.append("")
                section_label = section_title_from_stem(e.stem)
                lines.append(f"- [{section_label}]({verso_link(e.route)})")
            lines.append("")
        lines.append("-/")
        lines.append("")
        out = source_root / "Books" / book / "VersoHome.lean"
        out.write_text("\n".join(lines), encoding="utf-8")
        print(f"Wrote {out}")

    for paper in sorted([p.name for p in papers_root.iterdir() if p.is_dir()]):
        item_entries = by_paper.get(paper, [])
        item_entries = sorted(item_entries, key=lambda e: (e.section_num, e.part_num, e.stem))
        lines = []
        lines.append("/-!")
        lines.append(f"# {paper_title(paper)}")
        lines.append("")
        lines.append("This page provides an overview and navigation links for this paper.")
        lines.append("")
        lines.append("## Sections")
        lines.append("")
        if not item_entries:
            lines.append("No section pages have been generated yet.")
            lines.append("")
        else:
            for e in item_entries:
                section_label = section_title_from_stem(e.stem)
                lines.append(f"- [{section_label}]({verso_link(e.route)})")
            lines.append("")
        lines.append("-/")
        lines.append("")
        out = source_root / "Papers" / paper / "VersoHome.lean"
        out.write_text("\n".join(lines), encoding="utf-8")
        print(f"Wrote {out}")


def write_book_readmes(source_root: Path, entries: list[Entry]) -> None:
    books_root = source_root / "Books"
    all_books = sorted([p.name for p in books_root.iterdir() if p.is_dir()])

    by_book: dict[str, list[Entry]] = {book: [] for book in all_books}
    for e in entries:
        if e.category == "books":
            by_book.setdefault(e.book_or_paper, []).append(e)

    for book in all_books:
        title = book_title(book)
        home_route = normalize_path(f"books/{book.lower()}/home/")
        home_module = f"Books.{book}.VersoHome"
        book_module = f"Books.{book}.Book"
        book_file = books_root / book / "Book.lean"
        item_entries = sorted(
            [e for e in by_book.get(book, []) if (not e.is_home and e.section_num > 0 and e.part_num == 0)],
            key=lambda e: (e.chapter_num, e.section_num, e.part_num, e.stem),
        )
        out: list[str] = []
        out.append(f"# {title}")
        out.append("")
        if book in TBD_BOOKS:
            out.append("- Verso home: TBD")
            out.append("- API docs: TBD")
            out.append("- Lean source: TBD")
            out.append("- Verso home source: TBD")
        else:
            out.append(f"- Verso home: [{verso_link(home_route)}]({verso_link(home_route)})")
            out.append(f"- API docs: [{doc_link(book_module)}]({doc_link(book_module)})")
            if book_file.exists():
                out.append(f"- Lean source: [{GITHUB_SOURCE_BASE}Books/{book}/Book.lean]({GITHUB_SOURCE_BASE}Books/{book}/Book.lean)")
            else:
                out.append(f"- Lean source root: [{GITHUB_SOURCE_BASE}Books/{book}/]({GITHUB_SOURCE_BASE}Books/{book}/)")
            out.append(f"- Verso home source: [{source_link(home_module)}]({source_link(home_module)})")
        out.append("")

        if not item_entries:
            out.append("- (TODO: no chapter/section modules discovered yet)")
            out.append("")
        else:
            current_chapter = None
            for e in item_entries:
                if current_chapter != e.chapter_num:
                    current_chapter = e.chapter_num
                    out.append(f"## {chapter_label(current_chapter)}")
                    out.append("")
                out.append(
                    f"- {section_title_from_stem(e.stem)} "
                    f"([Verso]({verso_link(e.route)})) "
                    f"([API docs]({doc_link(e.module)})) "
                    f"([Lean source]({source_link(e.module)}))"
                )
            out.append("")

        readme = books_root / book / "README.md"
        readme.write_text("\n".join(out), encoding="utf-8")
        print(f"Wrote {readme}")


def write_paper_readmes(source_root: Path, entries: list[Entry]) -> None:
    papers_root = source_root / "Papers"
    all_papers = sorted([p.name for p in papers_root.iterdir() if p.is_dir()])

    by_paper: dict[str, list[Entry]] = {paper: [] for paper in all_papers}
    for e in entries:
        if e.category == "papers":
            by_paper.setdefault(e.book_or_paper, []).append(e)

    for paper in all_papers:
        title = paper_title(paper)
        home_route = normalize_path(f"papers/{paper.lower()}/home/")
        home_module = f"Papers.{paper}.VersoHome"
        paper_file = papers_root / paper / "Paper.lean"
        if paper_file.exists():
            paper_module = f"Papers.{paper}.Paper"
        else:
            paper_module = f"Papers.{paper}.Main"
        item_entries = sorted(
            [e for e in by_paper.get(paper, []) if (not e.is_home and e.section_num > 0 and e.part_num == 0)],
            key=lambda e: (e.section_num, e.part_num, e.stem),
        )
        out: list[str] = []
        out.append(f"# {title}")
        out.append("")
        out.append(f"- Verso home: [{verso_link(home_route)}]({verso_link(home_route)})")
        out.append(f"- API docs: [{doc_link(paper_module)}]({doc_link(paper_module)})")
        if paper_file.exists():
            out.append(f"- Lean source: [{GITHUB_SOURCE_BASE}Papers/{paper}/Paper.lean]({GITHUB_SOURCE_BASE}Papers/{paper}/Paper.lean)")
        else:
            out.append(f"- Lean source: [{GITHUB_SOURCE_BASE}Papers/{paper}/Main.lean]({GITHUB_SOURCE_BASE}Papers/{paper}/Main.lean)")
        out.append(f"- Verso home source: [{source_link(home_module)}]({source_link(home_module)})")
        out.append("")

        if not item_entries:
            out.append("- (TODO: no section modules discovered yet)")
            out.append("")
        else:
            out.append("## Sections")
            out.append("")
            for e in item_entries:
                out.append(
                    f"- {section_title_from_stem(e.stem)} "
                    f"([Verso]({verso_link(e.route)})) "
                    f"([API docs]({doc_link(e.module)})) "
                    f"([Lean source]({source_link(e.module)}))"
                )
            out.append("")

        readme = papers_root / paper / "README.md"
        readme.write_text("\n".join(out), encoding="utf-8")
        print(f"Wrote {readme}")


def main() -> None:
    args = parse_args()
    if args.repo_root is None:
        repo_root = Path(__file__).resolve().parents[2]
    else:
        repo_root = Path(args.repo_root).resolve()

    source_root = repo_root / "ReasBook"
    out_file = repo_root / "ReasBookWeb" / "ReasBookSite" / "Sections.lean"
    route_file = repo_root / "ReasBookWeb" / "ReasBookSite" / "RouteTable.lean"

    if not (source_root / "lakefile.lean").exists() and not (source_root / "lakefile.toml").exists():
        raise SystemExit(f"Lean project not found at {source_root}")

    entries = collect_entries(source_root)
    write_verso_home_modules(source_root, entries)
    out_file.parent.mkdir(parents=True, exist_ok=True)
    out_file.write_text(emit_sections(entries), encoding="utf-8")
    route_file.write_text(emit_route_table(entries), encoding="utf-8")
    write_book_readmes(source_root, entries)
    write_paper_readmes(source_root, entries)
    print(f"Wrote {out_file} with {len(entries)} sections")
    print(f"Wrote {route_file} with generated route macro")


if __name__ == "__main__":
    main()
