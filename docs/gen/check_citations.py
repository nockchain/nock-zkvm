#!/usr/bin/env python3
"""Check every `name` file:line citation in the given Markdown files: the cited line must contain the name as a whole
identifier (a declaration line, for generated citations). Exit 1 if any citation fails.
Usage: python3 docs/gen/check_citations.py docs/SPEC.md [more.md ...]"""
import re
import sys

PAIR = re.compile(r"`(?:[A-Za-z0-9_/]+\.lean::)?([A-Za-z_][A-Za-z0-9_.']*)` \(?((?:`?[A-Za-z0-9_/.\-]+\.lean:\d+`?(?:–`\d+`)?(?:, (?:sound at )?`:\d+`)*(?:, )?)+)")
RANGE = re.compile(r"\.lean:(\d+)`?–`(\d+)`")
SHORT = re.compile(r"`:(\d+)`")
LOC = re.compile(r"([A-Za-z0-9_/.\-]+\.lean):(\d+)")
bad = n = 0
for md in sys.argv[1:]:
    # join line breaks first: a citation whose name and location sit on two lines is checked too
    text = re.sub(r"[ \t]*\n[ \t]*", " ", open(md, encoding="utf-8").read())
    for name, locs in PAIR.findall(text):
        short = name.split(".")[-1]
        rng = RANGE.search(locs)
        extra = [int(x) for x in SHORT.findall(locs)]  # `name_sound` paired with a same-file `:N` shorthand
        for path, line in LOC.findall(locs):
            n += 1
            lines = []
            for base in ("", "nockvm-e2e/", "nockvm-e2e/NockvmE2E/"):  # SPEC §9-§10 cite paths under nockvm-e2e/NockvmE2E/
                try:
                    lines = open(base + path, encoding="utf-8").read().split("\n")
                    break
                except OSError:
                    continue
            nums = [int(line)] + extra
            if rng:  # `file:a`–`b`: the name may sit on any line a..b
                nums += list(range(int(rng.group(1)), int(rng.group(2)) + 1))
            srcs = [lines[k - 1] for k in nums if 0 < k <= len(lines)]
            src = srcs[0] if srcs else ""
            if not any(re.search(r"(?<![A-Za-z0-9_'])" + re.escape(short) + r"(?![A-Za-z0-9_'])", t) for t in srcs):
                bad += 1
                print(f"{md}: `{name}` {path}:{line}: {src.strip()[:90]!r}")
print(f"{n} citations checked, {bad} failed", file=sys.stderr)
sys.exit(1 if bad else 0)
