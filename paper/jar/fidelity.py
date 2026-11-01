#!/usr/bin/env python3
"""Compare the LIPIcs and JAR versions of Paper D, for FIDELITY.md.

Usage: python3 fidelity.py LIPICS_DIR JAR_DIR
where each directory holds a built main.tex, main.bbl and main.pdf (run latexmk first).

Two checks:
1. Source: every line of the LIPIcs main.tex from the Introduction to the end of the
   appendices must occur, in order, in the JAR main.tex; lines added or removed are printed.
2. PDF text (pdftotext): both texts are normalised, then compared character by character:
   - page numbers, the LIPIcs running heads, and theorem/proof end marks are dropped;
   - bracketed citation numbers become "[cite]" (the two styles number the references
     differently; the cited keys are covered by check 1);
   - itemize bullets are dropped (LIPIcs and sn-jnl draw them differently);
   - the reference lists are cut out (they are compared by key: same entries, other style);
   - whitespace and hyphens are removed, so that line breaks, hyphenation and math spacing
     (which differ with the text width and fonts) do not show up.
   Every remaining difference is printed with context; a deleted chunk that is also inserted
   elsewhere is reported once, as moved.
"""
import re
import subprocess
import sys
import difflib
from pathlib import Path

lip_dir, jar_dir = Path(sys.argv[1]), Path(sys.argv[2])

# ---------------------------------------------------------------- 1. source
lip_src = (lip_dir / "main.tex").read_text(encoding="utf-8").split("\n")
jar_src = (jar_dir / "main.tex").read_text(encoding="utf-8").split("\n")
start = next(i for i, l in enumerate(lip_src) if l.startswith(r"\section{Introduction}")) - 1
end = lip_src.index(r"\end{document}")
body = lip_src[start:end]
sm = difflib.SequenceMatcher(None, body, jar_src, autojunk=False)
print("== 1. Source lines (LIPIcs body vs JAR file) ==")
for op, i1, i2, j1, j2 in sm.get_opcodes():
    if op == "equal":
        continue
    # Ignore the JAR preamble/front matter (before the body starts) and the closing lines.
    if i1 == 0 or i1 == len(body):
        continue
    for l in body[i1:i2]:
        print(f"  - {l}")
    for l in jar_src[j1:j2]:
        print(f"  + {l}")
    print("  --")
matched = sum(b.size for b in sm.get_matching_blocks())
print(f"  {matched} of {len(body)} body lines copied unchanged\n")


# ---------------------------------------------------------------- 2. PDF text
def bib_keys(bbl):
    t = bbl.read_text(encoding="utf-8")
    return re.findall(r"\\bibitem(?:\[(?:[^\[\]]|\[[^\]]*\])*\])?\s*\{([^}]+)\}", t)


def pdf_text(d, refs_heading_re, refs_end_re):
    t = subprocess.run(["pdftotext", str(d / "main.pdf"), "-"], capture_output=True,
                       text=True, check=True).stdout
    for a, b in [("ﬁ", "fi"), ("ﬂ", "fl"), ("ﬀ", "ff"), ("ﬃ", "ffi"), ("ﬄ", "ffl")]:
        t = t.replace(a, b)
    lines = []
    for page in t.split("\f"):
        pl = page.split("\n")
        nonempty = [i for i, l in enumerate(pl) if l.strip()]
        edge = set(nonempty[:3] + nonempty[-3:])
        for i, l in enumerate(pl):
            s = l.strip()
            if i in edge and re.fullmatch(r"\d+", s):   # page numbers (header or footer)
                continue
            if s in ("Machine-Checked Complexity of Decision-Table Completeness",
                     "C. A. Russell"):                    # LIPIcs running heads
                continue
            lines.append(l)
    t = "\n".join(lines)
    # Cut the reference list.
    m = re.search(refs_heading_re, t, re.M)
    e = re.search(refs_end_re, t[m.end():], re.M) if refs_end_re else None
    refs = t[m.start(): m.end() + e.start()] if e else t[m.start():]
    t = t[: m.start()] + (t[m.end() + e.start():] if e else "")
    # Citation numbers differ between the two styles. Replace every bracketed number list
    # (with an optional note, e.g. "[11, Chapter 13]") by "[cite]". This also hits math such as
    # "[3, 2]", identically in both texts; the cited keys themselves are checked by check 1,
    # since every \cite is in a body line.
    t = re.sub(r"\[\d+(?:[–-]\d+)?(?:,\s*(?:\d+(?:[–-]\d+)?|[^\],\[]+))*\]", "[cite]", t)
    for mark in "▶◀□∎•":
        t = t.replace(mark, "")
    return t, refs


lip_keys = bib_keys(lip_dir / "main.bbl")
jar_keys = bib_keys(jar_dir / "main.bbl")
lip_t, lip_refs = pdf_text(lip_dir, r"^References$", r"^(?:A\s*\n\s*)?Main Lean statements$")
jar_t, jar_refs = pdf_text(jar_dir, r"^References$", None)

print("== 2a. Reference lists ==")
print(f"  LIPIcs: {len(lip_keys)} entries; JAR: {len(jar_keys)} entries; "
      f"same keys: {sorted(lip_keys) == sorted(jar_keys)}\n")


def canon(t):
    # Remove whitespace and hyphens; keep a map back to the original for context.
    chars, pos = [], []
    for i, c in enumerate(t):
        if c.isspace() or c in "-‐":
            continue
        chars.append(c)
        pos.append(i)
    return "".join(chars), pos


a, apos = canon(lip_t)
b, bpos = canon(jar_t)
sm = difflib.SequenceMatcher(None, a, b, autojunk=False)
ops = [o for o in sm.get_opcodes() if o[0] != "equal"]
deleted = {a[i1:i2] for op, i1, i2, j1, j2 in ops if op in ("delete", "replace") and i2 - i1 > 20}
inserted = {b[j1:j2] for op, i1, i2, j1, j2 in ops if op in ("insert", "replace") and j2 - j1 > 20}
moved = deleted & inserted

print("== 2b. PDF text differences (whitespace and hyphens ignored) ==")
n = 0
for op, i1, i2, j1, j2 in ops:
    da, db = a[i1:i2], b[j1:j2]
    if da in moved and not db:
        print(f"  [moved] {lip_t[apos[i1]:apos[i2 - 1] + 1][:160]!r}")
        continue
    if db in moved and not da:
        continue
    n += 1
    ctx = lip_t[apos[max(0, i1 - 40)]:apos[min(i1, len(apos) - 1)]].replace("\n", " ")
    la = lip_t[apos[i1]:apos[i2 - 1] + 1] if i2 > i1 else ""
    lb = jar_t[bpos[j1]:bpos[j2 - 1] + 1] if j2 > j1 else ""
    print(f"  [{n}] {op}: after {ctx[-60:]!r}\n      LIPIcs: {la[:400]!r}{" …(%d chars)" % len(la) if len(la) > 400 else ""}\n      JAR:    {lb[:400]!r}{" …(%d chars)" % len(lb) if len(lb) > 400 else ""}\n      JAR end: {lb[-200:]!r}")
print(f"\n  {n} differences besides moves; {len(a)} vs {len(b)} normalised characters")
