## Project 2: Homotopy Invariance of Singular Homology

## Personal Info

```
First & last name: Jasper Ganten
Project topic: Homotopy invariance of singular homology
Partner (optional): -
```

---

## Main Results

**File:** `LeanCourse25/Projects/HomotopyInvariance/BasicRewrite.lean`

This project develops categorical infrastructure for homotopy invariance of singular homology:

1. **General categorical framework** for the "evaluation from a point" pattern using Yoneda/coyoneda
2. **Natural transformation `toTopObjMkNat`** sending 0-simplices to their geometric realization, with naturality derived categorically
3. **Structures for homotopy** (`SimplicialHomotopy`, `MyHomotopy`) connecting simplicial and topological notions
4. **The connecting map** `DeltaOneToContinuousI` relating `|Δ[1]|` to the topological interval `I`

## What Is Not Included

The final steps of the homotopy invariance proof are **not included** because Joël Riou and Fabian Odermatt already have this as a PR to Mathlib:
- `SSet.Homotopy` → homotopy of singular chains → invariance of homology under homotopy

This project focuses on the categorical approach to the setup, not duplicating work already heading to Mathlib. See:

- https://github.com/leanprover-community/mathlib4/pull/32881
- https://github.com/leanprover-community/mathlib4/pull/33683

## References

Joël Riou's [`topcat-model-category`](https://github.com/joelriou/topcat-model-category) — several definitions (homeomorphisms between standard simplices and realizations) were adapted from there`. Especially the uniqueness lemmas for the terminal object were generalized and abstracted in my project.

## AI Tools Used

- **GitHub Copilot with lean-lsp MCP** — used to create 'lecture-style' files to understand API, refactoring and troubleshooting
- **Aristotle** — used for generating context and understanding Mathlib structure

AI was used throughout for suggestions and refactoring.
