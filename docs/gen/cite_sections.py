#!/usr/bin/env python3
"""Add or refresh a generated "Sources" line at the end of each subsection of docs/SPEC.md.

For every subsection, every Lean name written in code font (`name`, `Ns.name` or `File.lean::name`) that resolves to a
declaration in the source tree is listed with its `file:line`. A name that matches several declarations is resolved by
a file named in the same subsection (`File.lean`, `File.lean::name`) or by its qualified prefix; if it stays ambiguous it is
listed with every location. Names that resolve to nothing (notation, binders, values) are left out.

Usage: python3 docs/gen/cite_sections.py --root . --spec docs/SPEC.md [--sections 1-7,11]
The lines it writes start with SRC_MARK and are replaced on every run; nothing else in the file is changed.
"""
import argparse
import os
import re
import sys

sys.path.insert(0, os.path.dirname(__file__))
from theorem_index import index_decls  # noqa: E402

SRC_MARK = "<sub>Sources (generated):"
HEAD = re.compile(r"^(#{2,4}) (\d+(?:\.\d+)*)\.? ")
CODE = re.compile(r"`([^`]+)`")
IDENT = re.compile(r"^(?:([A-Za-z0-9_/]+\.lean)::)?([A-Za-z_][A-Za-z0-9_.']*)$")


def parse_ranges(spec):
    out = set()
    for part in spec.split(","):
        a, _, b = part.partition("-")
        for n in range(int(a), int(b or a) + 1):
            out.add(str(n))
    return out


LEAD = re.compile(r"^(?:([A-Za-z0-9_/]+\.lean)::)?([A-Za-z_][A-Za-z0-9_.']*)(?=$|[\s:(])")


def resolve(tok, decls, files_here):
    m = LEAD.match(tok.strip())
    if not m:
        return None
    fhint, name = m.group(1), m.group(2).rstrip(".")
    if len(name) < 3:
        return None
    short = name.split(".")[-1]
    cands = decls.get(short, [])
    if not cands:
        return None
    if "." in name:
        q = [c for c in cands if c[2].endswith(name)]
        cands = q or cands
    if fhint:
        q = [c for c in cands if c[0].endswith(fhint)]
        cands = q or cands
    in_here = [c for c in cands if os.path.basename(c[0]) in files_here]
    if len(cands) > 1 and in_here:
        cands = in_here
    # a bare lower-case word (`sem`, `empty`, `compile`) is cited only when it is unambiguous and long,
    # or when its file is named in the same subsection
    if "." not in name and not fhint and re.fullmatch(r"[a-z]+", name):
        if not in_here and (len(cands) > 1 or len(name) < 6):
            return None
    return short, cands


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", required=True)
    ap.add_argument("--spec", required=True)
    ap.add_argument("--sections", default="1-7,11")
    a = ap.parse_args()
    want = parse_ranges(a.sections)
    decls = index_decls(a.root)
    lines = [ln for ln in open(a.spec, encoding="utf-8").read().split("\n") if not ln.startswith(SRC_MARK)]

    # subsection boundaries
    marks = [i for i, ln in enumerate(lines) if HEAD.match(ln)] + [len(lines)]
    out, stats = [], {"sections": 0, "cited": 0, "ambiguous": 0}
    out.extend(lines[:marks[0]])
    for k in range(len(marks) - 1):
        s, e = marks[k], marks[k + 1]
        block = lines[s:e]
        num = HEAD.match(block[0]).group(2)
        while block and block[-1].strip() == "":
            block.pop()
        if num.split(".")[0] in want:
            text = "\n".join(block)
            files_here = set(os.path.basename(f) for f in re.findall(r"[A-Za-z0-9_/]+\.lean", text))
            seen, cites = set(), []
            for tok in CODE.findall(text):
                r = resolve(tok, decls, files_here)
                if not r:
                    continue
                short, cands = r
                if short in seen:
                    continue
                seen.add(short)
                locs = ", ".join(f"{c[0]}:{c[1]}" for c in cands[:4]) + (" …" if len(cands) > 4 else "")
                tag = " (several)" if len(cands) > 1 else ""
                stats["ambiguous"] += bool(tag)
                cites.append(f"`{short}` {locs}{tag}")
            if cites:
                stats["sections"] += 1
                stats["cited"] += len(cites)
                block += ["", SRC_MARK + " " + "; ".join(cites) + "</sub>"]
        out.extend(block + [""])
    open(a.spec, "w", encoding="utf-8").write("\n".join(out).rstrip("\n") + "\n")
    print(stats, file=sys.stderr)


if __name__ == "__main__":
    main()
