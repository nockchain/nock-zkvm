#!/usr/bin/env python3
"""Generate docs/THEOREMS.md (headline index) and docs/theorems-all.tsv (every recorded axioms line).

Inputs (nothing is built or run here):
  --root    the source tree (this repository's root)
  --log     LABEL=PATH, repeatable: a build log containing Lean `#print axioms` output
            ("'<name>' depends on axioms: [...]" or "'<name>' does not depend on any axioms").
            LABEL names the source in the output (e.g. the build that produced the log).
  --headlines  docs/gen/headlines.txt: one entry per line, "<section> | <short or qualified name> | <role>";
            lines starting with # are comments.
  --rev     the commit the source tree is at (printed in the header).
  --cited   a Markdown file (repeatable): its `name` (`file.lean:N`) citations are checked against the recorded lines,
            and those without one are written to --unrecorded (default docs/theorems-unrecorded.tsv).

For each headline the index gives: the declaration's file:line in the source tree, the statement head (from the
declaration keyword up to the first ':=' or a final 'by', whitespace collapsed, truncated), and the recorded axioms
line with its source label. A headline with no recorded line is listed as "no recorded line"; a short name that matches
more than one declaration is listed with every match and marked AMBIGUOUS. Nothing is inferred beyond that.
"""
import argparse
import os
import re
import sys
from collections import defaultdict

KW = r"(?:theorem|lemma|def|abbrev|structure|inductive|class|instance|noncomputable def|private theorem|private def|protected theorem|protected def)"
AX_RE = re.compile(r"'([^']+(?:'+)?)' (depends on axioms: \[([^\]]*)\]|does not depend on any axioms)")
STD = {"propext", "Classical.choice", "Quot.sound"}


def joined_entries(f):
    """Yield the log's lines with each wrapped axioms entry joined: Lean wraps a long
    "'<name>' depends on axioms: [propext,\n  Classical.choice,\n  Quot.sound]" over several lines; the entry continues
    until the closing ']'."""
    buf = None
    for line in f:
        line = line.rstrip("\n")
        if buf is not None:
            buf += " " + line.strip()
            if "]" in line:
                yield buf
                buf = None
            continue
        i = line.find("depends on axioms: [")
        if i >= 0 and "]" not in line[i:]:
            buf = line
            continue
        yield line
    if buf is not None:
        yield buf


def read_logs(specs):
    """Return {qualified name: (axioms tuple, label)}. A name seen with different lines in different logs is reported."""
    rec, clash = {}, []
    for spec in specs:
        label, _, path = spec.partition("=")
        with open(path, encoding="utf-8", errors="replace") as f:
            for line in joined_entries(f):
                # a name may end in one or more primes: match up to "' depends" / "' does"
                m = re.search(r"'(.+?)' (depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", line)
                if not m:
                    continue
                name = m.group(1)
                ax = tuple(a.strip() for a in m.group(3).split(",")) if m.group(3) is not None else ()
                # under `open Classical` Lean prints `Classical.choice` as `choice` (the tree declares no axiom of its own)
                ax = tuple("Classical.choice" if a == "choice" else a for a in ax)
                if name in rec and rec[name][0] != ax:
                    clash.append((name, rec[name], (ax, label)))
                rec.setdefault(name, (ax, label))
    return rec, clash


def lean_files(root):
    for d, dirs, files in os.walk(root):
        dirs[:] = [x for x in dirs if not x.startswith(".") and x != "vendor"]
        for fn in files:
            if fn.endswith(".lean"):
                yield os.path.join(d, fn)


def index_decls(root):
    """{short name: [(relpath, line, namespace-guess, head)]}"""
    decl_re = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?" + KW + r"\s+([^\s:({\[]+)")
    out = defaultdict(list)
    for path in lean_files(root):
        rel = os.path.relpath(path, root)
        with open(path, encoding="utf-8", errors="replace") as f:
            lines = f.readlines()
        ns = []
        for i, ln in enumerate(lines):
            m = re.match(r"^\s*namespace\s+(\S+)", ln)
            if m:
                ns.append(m.group(1))
                continue
            m = re.match(r"^\s*end\s+(\S+)\s*$", ln)
            if m and ns and ns[-1] == m.group(1):
                ns.pop()
                continue
            m = decl_re.match(ln)
            if not m:
                continue
            name = m.group(1)
            short = name.split(".")[-1]
            qual = ".".join(ns + [name])
            out[short].append((rel, i + 1, qual, head_of(lines, i)))
    return out


def head_of(lines, i, limit=400):
    buf = []
    joined = ""
    for ln in lines[i:i + 60]:
        buf.append(re.sub(r"\s--.*$", "", ln.rstrip("\n")).strip())
        joined = " ".join(buf)
        if ":=" in joined:
            joined = joined.split(":=")[0]
            break
        if re.search(r"\bby\s*$", joined):
            joined = re.sub(r"\bby\s*$", "", joined)
            break
    h = re.sub(r"\s+", " ", joined).strip()
    return h if len(h) <= limit else h[:limit] + " …"


def resolve(entry, decls, rec):
    """Match a headline (short or qualified) to declarations and to a recorded axioms line."""
    short = entry.split(".")[-1]
    cands = decls.get(short, [])
    if "." in entry:
        cands = [c for c in cands if c[2].endswith(entry)] or cands
    recs = [(q, v) for q, v in rec.items() if q == entry or q.endswith("." + entry)]
    if len(cands) > 1 and recs:  # narrow by the qualified names the logs recorded
        qs = {q for q, _ in recs}
        narrowed = [c for c in cands if any(q.endswith(c[2]) for q in qs)]
        cands = narrowed or cands
    return cands, recs


CITE = re.compile(r"`(?:[A-Za-z0-9_/]+\.lean::)?([A-Za-z_][A-Za-z0-9_.']*)` \(?`?([A-Za-z0-9_/.\-]+\.lean):(\d+)")
KIND = re.compile(r"\b(theorem|lemma|def|abbrev|structure|inductive|class|instance|opaque|axiom)\b")


def cited_unrecorded(mds, root, rec):
    """Declarations cited as `name` (`file.lean:N`) in the given Markdown files (line breaks joined), and those of them
    with no recorded axioms line: [(name, file:line, kind)]."""
    decls = index_decls(root)
    seen, cited = set(), []
    for md in mds:
        text = re.sub(r"[ \t]*\n[ \t]*", " ", open(md, encoding="utf-8").read())
        for name, path, line in CITE.findall(text):
            short = name.split(".")[-1]
            src = None
            for base in ("", "nockvm-e2e/", "nockvm-e2e/NockvmE2E/"):
                fp = os.path.join(root, base + path)
                if os.path.isfile(fp):
                    src, path = fp, base + path
                    break
            if src is None or (short, path) in seen:
                continue
            ls = open(src, encoding="utf-8", errors="replace").read().split("\n")
            ln = ls[int(line) - 1] if 0 < int(line) <= len(ls) else ""
            if not re.search(r"(?<![A-Za-z0-9_'])" + re.escape(short) + r"(?![A-Za-z0-9_'])", ln):
                continue  # not a declaration citation (checked separately by check_citations.py)
            seen.add((short, path))
            k = KIND.search(ln)
            # the qualified name of the declaration at that line (namespace guess from the index); recorded iff a log
            # printed that qualified name (a same-named declaration elsewhere does not count)
            quals = [c[2] for c in decls.get(short, []) if c[0] == path and c[1] == int(line)] or [name]
            hit = any(q == qq or q.endswith("." + qq) for q in rec for qq in quals)
            cited.append((name, f"{path}:{line}", k.group(1) if k else "other", hit))
    unrec = sorted((n, l, k) for n, l, k, hit in cited if not hit)
    return cited, unrec


def fmt_ax(ax):
    if not ax:
        return "none"
    s = ", ".join(ax)
    return s if set(ax) <= STD else s + " — NON-STANDARD"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", required=True)
    ap.add_argument("--log", action="append", default=[])
    ap.add_argument("--headlines", required=True)
    ap.add_argument("--rev", required=True)
    ap.add_argument("--out", default="docs/THEOREMS.md")
    ap.add_argument("--tsv", default="docs/theorems-all.tsv")
    ap.add_argument("--cited", action="append", default=[],
                    help="Markdown file whose `name` (`file.lean:N`) citations are checked against the recorded lines")
    ap.add_argument("--unrecorded", default="docs/theorems-unrecorded.tsv")
    a = ap.parse_args()

    rec, clash = read_logs(a.log)
    decls = index_decls(a.root)
    labels = ", ".join(s.partition("=")[0] for s in a.log)

    rows, missing, ambiguous = [], 0, 0
    with open(a.headlines, encoding="utf-8") as f:
        for ln in f:
            ln = ln.strip()
            if not ln or ln.startswith("#"):
                continue
            sec, name, role = [x.strip() for x in (ln.split("|") + ["", ""])[:3]]
            cands, recs = resolve(name, decls, rec)
            if not cands:
                loc, head, flag = "NOT FOUND in source", "", "NOT-FOUND"
                missing += 1
            else:
                loc = "<br>".join(f"`{c[0]}:{c[1]}`" for c in cands)
                head = cands[0][3]
                flag = "AMBIGUOUS" if len(cands) > 1 else ""
                ambiguous += bool(flag)
            if recs:
                axs = sorted({(fmt_ax(v[0]), v[1]) for _, v in recs})
                ax = "<br>".join(f"{x} ({lab})" for x, lab in axs)
            else:
                ax = "no recorded line"
            rows.append((sec, name, role, loc, head, ax, flag))

    cited, unrec = cited_unrecorded(a.cited, a.root, rec) if a.cited else ([], [])
    with open(a.out, "w", encoding="utf-8") as o:
        o.write("# Theorem index\n\n")
        o.write(f"Generated by `docs/gen/theorem_index.py` from the source tree at `{a.rev}` and the `#print axioms` output of: {labels}. "
                "Do not edit by hand; edit `docs/gen/headlines.txt` and re-run.\n\n")
        o.write("Columns: the declaration's location at that commit; its statement head (from the keyword to `:=`, "
                "whitespace collapsed, long heads truncated); the recorded axioms line and the log it comes from. "
                "\"no recorded line\" means none of the logs printed one: it is not a claim either way. "
                "Where a file opens `Classical`, Lean prints `Classical.choice` as `choice`; it is recorded here under its full name "
                "(the source tree declares no axiom of its own).\n\n")
        o.write(f"{len(rows)} headlines; {missing} not found; {ambiguous} ambiguous; {len(rec)} recorded axioms lines in all "
                f"(`docs/theorems-all.tsv`).\n\n")
        if a.cited:
            kinds = {}
            for _, _, k in unrec:
                kinds[k] = kinds.get(k, 0) + 1
            ks = ", ".join(f"{v} {k}" for k, v in sorted(kinds.items(), key=lambda x: -x[1]))
            o.write(f"Declarations cited with a location in {', '.join('`' + c + '`' for c in a.cited)}: {len(cited)}; "
                    f"with a recorded axioms line: {len(cited) - len(unrec)}; without one: {len(unrec)} ({ks}), listed in "
                    f"`docs/theorems-unrecorded.tsv`. These sources record no `#print axioms` line for them, and the documentation claims none.\n\n")
        cur = None
        for sec, name, role, loc, head, ax, flag in rows:
            if sec != cur:
                o.write(f"\n## {sec}\n\n| name | role | location | statement head | axioms |\n|---|---|---|---|---|\n")
                cur = sec
            h = head.replace("|", "\\|")
            o.write(f"| `{name}`{' **' + flag + '**' if flag else ''} | {role} | {loc} | `{h}` | {ax} |\n")
        if clash:
            o.write("\n## Conflicting recorded lines\n\n")
            for n, (ax1, l1), (ax2, l2) in clash:
                o.write(f"- `{n}`: {fmt_ax(ax1)} ({l1}) vs {fmt_ax(ax2)} ({l2})\n")

    with open(a.tsv, "w", encoding="utf-8") as t:
        t.write("name\taxioms\tsource\n")
        for n in sorted(rec):
            t.write(f"{n}\t{fmt_ax(rec[n][0])}\t{rec[n][1]}\n")

    if a.cited:
        with open(a.unrecorded, "w", encoding="utf-8") as t:
            t.write("name\tlocation\tkind\n")
            for n, loc, k in unrec:
                t.write(f"{n}\t{loc}\t{k}\n")
        print(f"{len(cited)} cited declarations, {len(unrec)} without a recorded line", file=sys.stderr)
    print(f"{len(rows)} headlines, {missing} not found, {ambiguous} ambiguous, {len(rec)} axioms lines, {len(clash)} clashes",
          file=sys.stderr)


if __name__ == "__main__":
    main()
