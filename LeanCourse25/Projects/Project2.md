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

### 1. Categorical framework for natural transformations from representables (§General)
- `evaluationFromPoint`: Given `pt : F(P)` for `F : D ⥤ Type`, constructs `Hom(P, -) ⟶ F` via coyoneda
- `natTransFromInitial`: For initial `I`, constructs `const(F(I)) ⟶ F`
- Uniqueness lemmas showing these are determined by their value at the distinguished object

### 2. Topological homotopy reformulation
- `MyHomotopy`: Category-friendly reformulation of `ContinuousMap.Homotopy` using `j_0, j_1 : X ⟶ X ⨯ I`
- `ContinuousMap.Homotopy.toMyHomotopy`: Converts Mathlib homotopies to the categorical form

### 3. Realization of 0-simplices via the categorical framework
- `eval₀IsoPointsFunctor`: Isomorphism `eval₀ ≅ Hom(Δ[0], -)` via Yoneda
- `toTopObjMkNat`: Natural transformation sending 0-simplices to points in `|X|`, constructed as composition with `evaluationFromPoint`
- Uniqueness: `toTopObjMkNat_unique` shows this is the unique such map

### 4. Building the simplicial homotopy
- `toTopEquivUnitInt : |Δ[1]| ≃ₜ TopCat.I` — homeomorphism between realization and interval
- `iota_I : Δ[1] ⟶ toSSet(I)` — adjoint transpose via `sSetTopAdj`
- `connecting_map X : toSSet(X) ⨯ Δ[1] ⟶ toSSet(X × I)` — the bridge map
- `topHomotopyToSimplicialHomotopy`: **Main theorem** — converts topological homotopy to `SimplicialHomotopy`

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
