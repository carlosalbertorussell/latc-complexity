# Releasing latc-complexity v1.0

Steps for the release that Paper D (Journal of Automated Reasoning version, `paper/jar/main.tex`)
cites as its artifact. **Steps 0–3 were done on 2026-11-01** (built and audited at commit `6a008ef`; the
tag `v1.0` is on the commit that records the build in the README, with the same Lean files). The repository is private; the paper cites the archive
as `[DOI at release]`. Each step needs the author's approval, and the steps
that publish something (4 and 5) cannot be undone.

## 0. Preconditions

* The JAR revision (branch `jar-revision`) is approved and merged into `main` by the author.
* `lean-toolchain`, `lakefile.toml` and `lake-manifest.json` still pin Lean `v4.36.0-rc1` and
  Complexitylib `b7acfc2310217697a892e791d318a5e127fadfd9`. Do not bump them for the release:
  the paper reports the build at this pin.
* `LICENSE` (MIT) is present, and `README.md` lists every main theorem.
* No `sorry`, `admit`, `native_decide` or `axiom` outside `#print axioms` lines:

  ```bash
  grep -rwn "sorry\|admit\|native_decide\|axiom" --include=*.lean LatcComplexity LatcFormal | grep -v "#print axioms"
  ```

  The command must print nothing.

## 1. Tag v1.0

On `main`, at the commit to be released:

```bash
git tag -a v1.0 -m "latc-complexity 1.0: the artifact of Paper D (JAR)"
```

```bash
git push origin v1.0
```

## 2. Cold build at the tag

Use a fresh machine or a fresh `HOME`, with no `~/.elan`, no `.lake` and no Mathlib cache. Record
the start and end of every step with `date`.

```bash
git clone https://github.com/carlosalbertorussell/latc-complexity && cd latc-complexity && git checkout v1.0
```

```bash
curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o elan-init.sh && sh elan-init.sh -y --default-toolchain none
```

```bash
lake exe cache get
```

```bash
lake build
```

Expected: `Build completed successfully (18651 jobs)`, exit code 0, no warnings, no errors.
Record the Lean, Lake and elan versions, the machine (cores, OS), the times and the disk used.

## 3. Full axiom audit at the tag

```bash
for f in LatcComplexity/Axioms.lean LatcComplexity/Valiant/Axioms.lean LatcFormal/Axioms.lean; do lake env lean $f; done > audit.txt
```

Check that:

* every `#print axioms` line has an answer (234, 94 and 69 lines at the JAR revision);
* every answer is a subset of `[propext, Classical.choice, Quot.sound]`;
* `sorryAx` and other axioms appear nowhere: `grep -c sorryAx audit.txt` prints `0`.

Expected at the JAR revision: `LatcComplexity/Axioms.lean` 234 (202 all three, 17
`[propext, Quot.sound]`, 13 `[propext]`, 2 `[Quot.sound]`); `LatcComplexity/Valiant/Axioms.lean`
94 (76 all three, 9 `[propext, Quot.sound]`, 7 `[propext]`, 2 none); `LatcFormal/Axioms.lean` 69
(66 all three, 3 `[propext, Quot.sound]`).

Write the figures of steps 2 and 3 into the README ("Verification status") and into Appendix C
of `paper/jar/main.tex`, replacing the build reported there if they differ, and commit.

## 4. Make the repository public

On GitHub: Settings → General → Danger Zone → Change visibility → Public. Before that, check
that no file holds anything that must stay private (the history included).

## 5. Archive on Zenodo

1. Log in to Zenodo with the author's account and enable the GitHub integration for
   `carlosalbertorussell/latc-complexity` (Zenodo → GitHub → toggle the repository).
2. On GitHub, create a release from the tag `v1.0` (Releases → Draft a new release → choose
   `v1.0`). Zenodo archives the release and mints a DOI.
3. On Zenodo, check the record: title, author (Carlos A. Russell, ORCID 0009-0003-3741-0230),
   licence MIT, version 1.0, and a link to the paper once published.
4. Optionally add a `CITATION.cff` with the DOI in a later commit (not part of the tag).

## 6. Cite the DOI

Replace every `[DOI at release]` in `paper/jar/main.tex` (Data availability, Code availability,
Appendix C) with the version DOI of step 5, add a `@software` entry for it to
`paper/extra.bib`, rebuild the paper and commit.
