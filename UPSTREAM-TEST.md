# Upstream build test: kept, not merged

**Decision (2026-10-31, the author):** keep this branch and leave it unmerged. Paper D ("Machine-Checked Complexity of Decision-Table Completeness in Lean", target: *Journal of Automated Reasoning*) stays pinned to complexitylib `b7acfc2` (Lean v4.36.0-rc1, CSLib f4a4725, Mathlib 625d891), the versions its text, README, cold-build figures and `docs/paper-facts.md` describe.

**What this branch shows:** with complexitylib upstream `b9e6241` (2026-10-31, Lean v4.36.0-rc2, CSLib 254e30e, Mathlib 6955275) and no Lean file changed, `lake build` completes (18,717 jobs, no warnings, no errors, no `sorry`) and the axiom audit is unchanged (300 theorems). The development is robust to that upstream move. Paper D may say so, citing this test and its date.

**Merge only if one of these holds:**

1. The pinned versions stop building from a fresh clone (for example the Mathlib cache or the toolchain for `b7acfc2` is no longer available).
2. JAR's editor or reviewers ask for current dependency versions, or report a build problem on the pinned ones.
3. A revision of Paper D needs a result or fix that exists only in a newer complexitylib.

**Before merging:** rebase on `main` (this branch was cut 22 commits behind), rerun `lake update complexitylib` on the then-current upstream, run a full cold build and the axiom audit, and update the README, the cold-build figures, every version mentioned in `paper/` (both the LIPIcs and the JAR versions) and the line numbers in `docs/paper-facts.md`. The author approves the merge.
