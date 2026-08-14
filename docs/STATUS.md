# Verification Status

## Verified modules

| Module | Verified declarations |
|---|---:|
| Set theory: relative complements | 2 |

## Acceptance criteria

A declaration is counted as verified only when:

1. its statement has explicit mathematical types and assumptions;
2. its proof is accepted by the pinned Lean toolchain;
3. it contains no `sorry`;
4. it does not replace an expected proof with a new axiom;
5. its dependencies are part of this repository or the pinned Mathlib version.
