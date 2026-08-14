# Verification Status

## Verified modules

| Module | Verified declarations |
|---|---:|
| Set theory: basic relations | 10 |
| Set theory: lattice and complement laws | 12 |
| Set theory: relative complements | 2 |
| Logic: basic equivalences | 3 |
| Algebra: equality and order basics | 5 |
| Algebra: strict inequalities | 8 |
| Algebra: elementary means | 4 |
| Algebra: mean and absolute-value inequalities | 6 |
| Algebra: quadratic equations | 2 |
| **Total** | **52** |

## Acceptance criteria

A declaration is counted as verified only when:

1. its statement has explicit mathematical types and assumptions;
2. its proof is accepted by the pinned Lean toolchain;
3. it contains no `sorry`;
4. it does not replace an expected proof with a new axiom;
5. its dependencies are part of this repository or the pinned Mathlib version.
